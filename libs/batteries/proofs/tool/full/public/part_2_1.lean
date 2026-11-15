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

-- Batteries.OrderedAssocList.merge_comm, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.merge_comm.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {β γ δ : Type} (f : α → Option β → Option γ → Option δ)
        (g : α → Option γ → Option β → Option δ),
        (∀ (a : α), g a Option.none Option.none = Option.none) →
          (∀ (a : α) (x : Option β) (y : Option γ), f a x y = g a y x) →
            ∀ (l₁ : Batteries.OrderedAssocList cmp β) (l₂ : Batteries.OrderedAssocList cmp γ), Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) _ (Nat) (Nat) (Nat) (fun (a : Bool) (a_1 a_2 : Option Nat) => Option.none) (fun (a : Bool) (a_1 a_2 : Option Nat) => Option.none) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  simp) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
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

-- Batteries.OrderedAssocList.merge_comm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.merge_comm.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] {β γ δ : Type}
        (f : α → Option β → Option γ → Option δ) (g : α → Option γ → Option β → Option δ),
        (∀ (a : α), g a Option.none Option.none = Option.none) →
          (∀ (a : α) (x : Option β) (y : Option γ), f a x y = g a y x) →
            ∀ (l₁ : Batteries.OrderedAssocList cmp β) (l₂ : Batteries.OrderedAssocList cmp γ), Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (Nat) (Nat) (Nat) (fun (a : Nat) (a_1 a_2 : Option Nat) => Option.none) (fun (a : Nat) (a_1 a_2 : Option Nat) => Option.none) (by
  simp) (by
  simp) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) Nat }) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) Nat })) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Batteries.OrderedAssocList.merge_mk_nil_mk_cons, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.merge_mk_nil_mk_cons.h2 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} [inst : @Std.TransCmp α cmp] {β γ δ : Type}
        {h : @Batteries.AssocList.KeysOrdered α β cmp (@Batteries.AssocList.nil α β)} {x' : α} {y' : γ}
        {t' : Batteries.AssocList α γ}
        {h' : @Batteries.AssocList.KeysOrdered α γ cmp (@Batteries.AssocList.cons α γ x' y' t')}
        {f : α → Option β → Option γ → Option δ}, @Std.LawfulEqCmp α cmp) := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) _ (Nat) (Nat) (Nat) (by
  decide) (Bool.false) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Bool Nat) (by
  decide) (fun (a : Bool) (a_1 a_2 : Option Nat) => @Option.none Nat)) (by
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

-- Batteries.OrderedAssocList.merge_mk_nil_mk_cons, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.merge_mk_nil_mk_cons.h3 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} [inst : @Std.LawfulEqCmp α cmp] {β γ δ : Type}
        {h : @Batteries.AssocList.KeysOrdered α β cmp (@Batteries.AssocList.nil α β)} {x' : α} {y' : γ}
        {t' : Batteries.AssocList α γ}
        {h' : @Batteries.AssocList.KeysOrdered α γ cmp (@Batteries.AssocList.cons α γ x' y' t')}
        {f : α → Option β → Option γ → Option δ}, @Std.TransCmp α cmp) := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (Nat) (Nat) (Nat) (by
  decide) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Nat Nat) (by
  decide) (fun (a : Nat) (a_1 a_2 : Option Nat) => @Option.none Nat)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Batteries.OrderedAssocList.merge_mk_nil_mk_cons, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.merge_mk_nil_mk_cons.h11 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} [inst : @Std.LawfulEqCmp α cmp] [inst : @Std.TransCmp α cmp] {β γ δ : Type}
        {h : @Batteries.AssocList.KeysOrdered α β cmp (@Batteries.AssocList.nil α β)} {x' : α} {y' : γ}
        {t' : Batteries.AssocList α γ} {f : α → Option β → Option γ → Option δ},
        @Batteries.AssocList.KeysOrdered α γ cmp (@Batteries.AssocList.cons α γ x' y' t')) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ _ (Nat) (Nat) (Nat) (by
  decide) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.cons Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Nat Nat)) (fun (a : Nat) (a_1 a_2 : Option Nat) => @Option.none Nat)) (by
  decide +kernel)

-- Batteries.UnionFind.setParentBump_rankD_lt, hypothesis 7: necessary
/- FAILED: 14:3: `simp` made no progress | 25:38: Function expected at
  (fun {arr' arr} {x y} {i} a =>
      Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl true)))
        (Lean.Omega.Constraint.combine_sat' (?m.152 a) (?m.154 a)))
    ?m.160
but this term has type
  False

Note: Expected a function because this term is being applied to the argument
  ⋯ | 2:112: missing end of character literal | 2:112: missing end of character literal | 11:26: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 146:42: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 10:118: missing end of character literal | 35:118: missing end of character literal
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.UnionFind.setParentBump_rankD_lt.h7 : ¬∀ {arr' arr : Array Batteries.UFNode} {x y : Fin arr.size},
        arr[↑x].rank < arr[↑y].rank ∨ arr[↑y].parent = ↑y →
          arr[↑x].rank ≤ arr[↑y].rank →
            ∀ {i : Nat},
              (Batteries.UnionFind.parentD arr' i = if ↑x = i then ↑y else Batteries.UnionFind.parentD arr i) →
                (∀ {i_1 : Nat},
                    Batteries.UnionFind.rankD arr' i_1 =
                      if ↑y = i_1 ∧ arr[↑x].rank = arr[↑y].rank then arr[↑y].rank + 1
                      else Batteries.UnionFind.rankD arr i_1) →
                  ¬Batteries.UnionFind.parentD arr' i = i →
                    Batteries.UnionFind.rankD arr' i < Batteries.UnionFind.rankD arr' (Batteries.UnionFind.parentD arr' i) := fun hc_h => absurd (@hc_h (#[{ parent := 0, rank := 0 : Batteries.UFNode }, { parent := 0, rank := 1 : Batteries.UFNode }]) (#[{ parent := 0, rank := 0 : Batteries.UFNode }, { parent := 0, rank := 1 : Batteries.UFNode }]) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  simp) (by
  decide)) (by
  decide +kernel)
-/

-- Batteries.UnionFind.setParentBump_rankD_lt, hypothesis 9: necessary
/- FAILED: 12:3: `simp` made no progress | 120:12: don't know how to synthesize placeholder for argument `b`
context:
arr' arr : Array Batteries.UFNode
x y : Fin arr.size
⊢ Prop

Note: All parameter types and holes (e.g., `_`) in the header of a theorem are resolved before the proof is processed; information from the proof cannot be used to infer what these values should be | 2:112: missing end of character literal | 2:112: missing end of character literal | 11:26: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 146:42: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 10:118: missing end of character literal | 35:118: missing end of character literal
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.UnionFind.setParentBump_rankD_lt.h9 : ¬∀ {arr' arr : Array Batteries.UFNode} {x y : Fin arr.size},
        arr[↑x].rank < arr[↑y].rank ∨ arr[↑y].parent = ↑y →
          arr[↑x].rank ≤ arr[↑y].rank →
            ∀ {i : Nat},
              (Batteries.UnionFind.parentD arr i ≠ i →
                  Batteries.UnionFind.rankD arr i < Batteries.UnionFind.rankD arr (Batteries.UnionFind.parentD arr i)) →
                (Batteries.UnionFind.parentD arr' i = if ↑x = i then ↑y else Batteries.UnionFind.parentD arr i) →
                  ¬Batteries.UnionFind.parentD arr' i = i →
                    Batteries.UnionFind.rankD arr' i < Batteries.UnionFind.rankD arr' (Batteries.UnionFind.parentD arr' i) := fun hc_h => absurd (@hc_h (#[{ parent := 0, rank := 0 : Batteries.UFNode }, { parent := 0, rank := 1 : Batteries.UFNode }]) (#[{ parent := 0, rank := 1 : Batteries.UFNode }, { parent := 0, rank := 0 : Batteries.UFNode }]) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (1) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  decide)) (by
  decide +kernel)
-/

-- Batteries.UnionFind.setParentBump_rankD_lt, hypothesis 10: necessary
/- FAILED: 15:3: `simp` made no progress | 26:40: Function expected at
  (fun {arr' arr} {x y} {i} a =>
      Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl true)))
        (Lean.Omega.Constraint.combine_sat' (?m.153 a) (?m.155 a)))
    ?m.161
but this term has type
  False

Note: Expected a function because this term is being applied to the argument
  ⋯ | 2:113: missing end of character literal | 2:113: missing end of character literal | 11:26: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 146:42: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 10:119: missing end of character literal | 35:119: missing end of character literal
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.UnionFind.setParentBump_rankD_lt.h10 : ¬∀ {arr' arr : Array Batteries.UFNode} {x y : Fin arr.size},
        arr[↑x].rank < arr[↑y].rank ∨ arr[↑y].parent = ↑y →
          arr[↑x].rank ≤ arr[↑y].rank →
            ∀ {i : Nat},
              (Batteries.UnionFind.parentD arr i ≠ i →
                  Batteries.UnionFind.rankD arr i < Batteries.UnionFind.rankD arr (Batteries.UnionFind.parentD arr i)) →
                (Batteries.UnionFind.parentD arr' i = if ↑x = i then ↑y else Batteries.UnionFind.parentD arr i) →
                  (∀ {i_1 : Nat},
                      Batteries.UnionFind.rankD arr' i_1 =
                        if ↑y = i_1 ∧ arr[↑x].rank = arr[↑y].rank then arr[↑y].rank + 1
                        else Batteries.UnionFind.rankD arr i_1) →
                    Batteries.UnionFind.rankD arr' i < Batteries.UnionFind.rankD arr' (Batteries.UnionFind.parentD arr' i) := fun hc_h => absurd (@hc_h (#[{ parent := 0, rank := 0 : Batteries.UFNode }, { parent := 0, rank := 1 : Batteries.UFNode }]) (#[{ parent := 0, rank := 0 : Batteries.UFNode }, { parent := 0, rank := 1 : Batteries.UFNode }]) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (2) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  simp)) (by
  decide +kernel)
-/

-- Batteries.AssocList.toList_orderedInsert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.toList_orderedInsert.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] {l : Batteries.AssocList α β},
        Batteries.AssocList.KeysOrdered cmp l →
          ∀ (a : α) (b : β),
            (Batteries.AssocList.orderedInsert cmp l a b).toList =
              List.filter (fun (p : α × β) => cmp a p.fst == Ordering.gt) l.toList ++
                (a, b) :: List.filter (fun (p : α × β) => cmp a p.fst == Ordering.lt) l.toList := fun hc_h => absurd (@hc_h (Nat) (Bool) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (Batteries.AssocList.cons 1 Bool.false (Batteries.AssocList.cons 0 Bool.false Batteries.AssocList.nil)) (by
  decide) (0) (Bool.false)) (by
  decide +kernel)

-- Batteries.AssocList.toList_orderedInsert, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.toList_orderedInsert.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] [inst : Std.TransCmp cmp]
        {l : Batteries.AssocList α β} (a : α) (b : β),
        (Batteries.AssocList.orderedInsert cmp l a b).toList =
          List.filter (fun (p : α × β) => cmp a p.fst == Ordering.gt) l.toList ++
            (a, b) :: List.filter (fun (p : α × β) => cmp a p.fst == Ordering.lt) l.toList := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ _ (Batteries.AssocList.cons 0 0 (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil)) (0) (0)) (by
  decide +kernel)

-- Std.TransCmp.le_trans, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TransCmp.le_trans.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering} {x y z : α},
        cmp x y ≠ Ordering.gt → cmp y z ≠ Ordering.gt → cmp x z ≠ Ordering.gt := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a % 3 = b % 3 then .eq else if (a + 1) % 3 = b % 3 then .lt else .gt : Nat → Nat → Ordering) (0) (1) (2) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.TransCmp.le_trans, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.le_trans.h6.inst : ¬(fun (a b : Nat) => Ord.compare a b) 1 0 ≠ Ordering.gt := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.le_trans.h6.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 ≠ Ordering.gt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TransCmp.le_trans.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {x y z : α},
        cmp y z ≠ Ordering.gt → cmp x z ≠ Ordering.gt := fun hc_h => HypCheckProof.Std.TransCmp.le_trans.h6.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) _ (1) (0) (0) HypCheckProof.Std.TransCmp.le_trans.h6.prem0)

-- Std.TransCmp.le_trans, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.le_trans.h7.inst : ¬(fun (a b : Nat) => Ord.compare a b) 1 0 ≠ Ordering.gt := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.le_trans.h7.prem0 : (fun (a b : Nat) => Ord.compare a b) 1 1 ≠ Ordering.gt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TransCmp.le_trans.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {x y z : α},
        cmp x y ≠ Ordering.gt → cmp x z ≠ Ordering.gt := fun hc_h => HypCheckProof.Std.TransCmp.le_trans.h7.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) _ (1) (1) (0) HypCheckProof.Std.TransCmp.le_trans.h7.prem0)

-- Batteries.OrderedAssocList.insert_mk_nil, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.insert_mk_nil.h2 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} [inst : @Std.OrientedCmp α cmp] {β : Type}
        {h : @Batteries.AssocList.KeysOrdered α β cmp (@Batteries.AssocList.nil α β)} {a : α} {b : β},
        @Std.LawfulEqCmp α cmp) := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) _ (Nat) (by
  decide) (Bool.false) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
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

-- Batteries.OrderedAssocList.insert_mk_nil, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.insert_mk_nil.h3 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} [inst : @Std.LawfulEqCmp α cmp] {β : Type}
        {h : @Batteries.AssocList.KeysOrdered α β cmp (@Batteries.AssocList.nil α β)} {a : α} {b : β},
        @Std.OrientedCmp α cmp) := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (Nat) (by
  decide) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  exact fun hc_c =>
    absurd (hc_c.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TransCmp.lt_of_le_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.lt_of_le_of_lt.h2.inst : ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.lt := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.lt_of_le_of_lt.h2.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 1 ≠ Ordering.gt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.lt_of_le_of_lt.h2.prem1 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 1 0 = Ordering.lt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TransCmp.lt_of_le_of_lt.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering} {x y z : α},
        cmp x y ≠ Ordering.gt → cmp y z = Ordering.lt → cmp x z = Ordering.lt := fun hc_h => HypCheckProof.Std.TransCmp.lt_of_le_of_lt.h2.inst (@hc_h (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (1) (0) HypCheckProof.Std.TransCmp.lt_of_le_of_lt.h2.prem0 HypCheckProof.Std.TransCmp.lt_of_le_of_lt.h2.prem1)

-- Std.TransCmp.lt_of_le_of_lt, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.lt_of_le_of_lt.h6.inst : ¬(fun (a b : Nat) => Ord.compare a b) 1 1 = Ordering.lt := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.lt_of_le_of_lt.h6.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 1 = Ordering.lt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TransCmp.lt_of_le_of_lt.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {x y z : α},
        cmp y z = Ordering.lt → cmp x z = Ordering.lt := fun hc_h => HypCheckProof.Std.TransCmp.lt_of_le_of_lt.h6.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) _ (1) (0) (1) HypCheckProof.Std.TransCmp.lt_of_le_of_lt.h6.prem0)

-- Std.TransCmp.lt_of_le_of_lt, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.lt_of_le_of_lt.h7.inst : ¬(fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.lt := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.lt_of_le_of_lt.h7.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 ≠ Ordering.gt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TransCmp.lt_of_le_of_lt.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {x y z : α},
        cmp x y ≠ Ordering.gt → cmp x z = Ordering.lt := fun hc_h => HypCheckProof.Std.TransCmp.lt_of_le_of_lt.h7.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) _ (0) (0) (0) HypCheckProof.Std.TransCmp.lt_of_le_of_lt.h7.prem0)

-- List.mem_diff_of_mem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_diff_of_mem.h2 : ¬∀ {α : Type} [inst : BEq α] {a : α} {l₁ l₂ : List α}, a ∈ l₁ → ¬a ∈ l₂ → a ∈ l₁.diff l₂ := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (0) ([0]) ([1]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.mem_diff_of_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_diff_of_mem.h6 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : LawfulBEq α] {a : α} {l₁ l₂ : List α}, ¬a ∈ l₂ → a ∈ l₁.diff l₂ := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ (0) ([]) ([]) (by
  decide)) (by
  decide +kernel)

-- List.mem_diff_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_diff_of_mem.h7 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : LawfulBEq α] {a : α} {l₁ l₂ : List α}, a ∈ l₁ → a ∈ l₁.diff l₂ := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ (0) ([0]) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.getElem_swap_of_ne, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_swap_of_ne.h5 : Not
      (∀ {α : Type} {xs : List α} {i j k : Nat},
        @Ne Nat k j →
          ∀ (hk : @LT.lt Nat instLTNat k (@List.length α (@List.swap α xs i j))),
            @Eq α
              (@GetElem.getElem (List α) Nat α (fun (as : List α) (i : Nat) => @LT.lt Nat instLTNat i (@List.length α as))
                (@List.instGetElemNatLtLength α) (@List.swap α xs i j) k hk)
              (@GetElem.getElem (List α) Nat α (fun (as : List α) (i : Nat) => @LT.lt Nat instLTNat i (@List.length α as))
                (@List.instGetElemNatLtLength α) xs k
                (@Eq.rec Nat (@List.length α (@List.swap α xs i j))
                  (fun (x : Nat) (h : @Eq Nat (@List.length α (@List.swap α xs i j)) x) => @LT.lt Nat instLTNat k x) hk
                  (@List.length α xs) (@List.length_swap α i j xs)))) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hc_k0 hc_k1) (by
  decide +kernel)

-- List.getElem_swap_of_ne, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_swap_of_ne.h6 : Not
      (∀ {α : Type} {xs : List α} {i j k : Nat},
        @Ne Nat k i →
          ∀ (hk : @LT.lt Nat instLTNat k (@List.length α (@List.swap α xs i j))),
            @Eq α
              (@GetElem.getElem (List α) Nat α (fun (as : List α) (i : Nat) => @LT.lt Nat instLTNat i (@List.length α as))
                (@List.instGetElemNatLtLength α) (@List.swap α xs i j) k hk)
              (@GetElem.getElem (List α) Nat α (fun (as : List α) (i : Nat) => @LT.lt Nat instLTNat i (@List.length α as))
                (@List.instGetElemNatLtLength α) xs k
                (@Eq.rec Nat (@List.length α (@List.swap α xs i j))
                  (fun (x : Nat) (h : @Eq Nat (@List.length α (@List.swap α xs i j)) x) => @LT.lt Nat instLTNat k x) hk
                  (@List.length α xs) (@List.length_swap α i j xs)))) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hc_k0 hc_k1) (by
  decide +kernel)

-- List.getElem_swap_of_ne, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_swap_of_ne.h7 : ¬∀ {α : Type} {xs : List α} {i j k : Nat}, k ≠ i → k ≠ j → k < (xs.swap i j).length := fun hc_h => absurd (@hc_h (Nat) ([]) (0) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Batteries.OrderedAssocList.toAssocList_merge, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.toAssocList_merge.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {β α_1 α_2 : Type}
        {f : α → Option β → Option α_1 → Option α_2} {l₂ : Batteries.OrderedAssocList cmp α_1}
        {l₁ : Batteries.OrderedAssocList cmp β}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) _ (Nat) (Nat) (Nat) (fun (a : Bool) (a_1 a_2 : Option Nat) => Option.none) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
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

-- Batteries.OrderedAssocList.toAssocList_merge, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.toAssocList_merge.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] {β α_1 α_2 : Type}
        {f : α → Option β → Option α_1 → Option α_2} {l₂ : Batteries.OrderedAssocList cmp α_1}
        {l₁ : Batteries.OrderedAssocList cmp β}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (Nat) (Nat) (Nat) (fun (a : Nat) (a_1 a_2 : Option Nat) => Option.none) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) Nat }) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) Nat })) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Batteries.BinaryHeap.decreaseKey_wf, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.decreaseKey_wf.h6 : ¬∀ {α : Type} {x : α} [inst : Ord α] [inst_1 : Std.TransOrd α] {heap : Batteries.BinaryHeap α} {i : Fin heap.size},
        (Ord.compare (heap.get i) x).isGE = Bool.true → (heap.decreaseKey i x).WF := fun hc_h => absurd (@hc_h (Nat) (1) (instOrdNat) _ ({ arr := #[0, 1] : Batteries.BinaryHeap Nat }) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- Std.TransCmp.gt_of_gt_of_ge, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.gt_of_gt_of_ge.h2.inst : ¬(fun (a b : Nat) => if a % 3 = b % 3 then Ordering.eq else if (a + 1) % 3 = b % 3 then Ordering.lt else Ordering.gt) 0
          1 =
        Ordering.gt := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.gt_of_gt_of_ge.h2.prem0 : (fun (a b : Nat) => if a % 3 = b % 3 then Ordering.eq else if (a + 1) % 3 = b % 3 then Ordering.lt else Ordering.gt) 0
        2 =
      Ordering.gt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.gt_of_gt_of_ge.h2.prem1 : (fun (a b : Nat) => if a % 3 = b % 3 then Ordering.eq else if (a + 1) % 3 = b % 3 then Ordering.lt else Ordering.gt) 2
        1 ≠
      Ordering.lt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TransCmp.gt_of_gt_of_ge.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering} {x y z : α},
        cmp x y = Ordering.gt → cmp y z ≠ Ordering.lt → cmp x z = Ordering.gt := fun hc_h => HypCheckProof.Std.TransCmp.gt_of_gt_of_ge.h2.inst (@hc_h (Nat) (fun (a b : Nat) => if a % 3 = b % 3 then Ordering.eq else if (a + 1) % 3 = b % 3 then Ordering.lt else Ordering.gt) (0) (2) (1) HypCheckProof.Std.TransCmp.gt_of_gt_of_ge.h2.prem0 HypCheckProof.Std.TransCmp.gt_of_gt_of_ge.h2.prem1)

-- Std.TransCmp.gt_of_gt_of_ge, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.gt_of_gt_of_ge.h6.inst : ¬(fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.gt := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.gt_of_gt_of_ge.h6.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 ≠ Ordering.lt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TransCmp.gt_of_gt_of_ge.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {x y z : α},
        cmp y z ≠ Ordering.lt → cmp x z = Ordering.gt := fun hc_h => HypCheckProof.Std.TransCmp.gt_of_gt_of_ge.h6.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) _ (0) (0) (0) HypCheckProof.Std.TransCmp.gt_of_gt_of_ge.h6.prem0)

-- Std.TransCmp.gt_of_gt_of_ge, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.gt_of_gt_of_ge.h7.inst : ¬(fun (a b : Nat) => Ord.compare a b) 1 1 = Ordering.gt := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.gt_of_gt_of_ge.h7.prem0 : (fun (a b : Nat) => Ord.compare a b) 1 0 = Ordering.gt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TransCmp.gt_of_gt_of_ge.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {x y z : α},
        cmp x y = Ordering.gt → cmp x z = Ordering.gt := fun hc_h => HypCheckProof.Std.TransCmp.gt_of_gt_of_ge.h7.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) _ (1) (0) (1) HypCheckProof.Std.TransCmp.gt_of_gt_of_ge.h7.prem0)

-- Batteries.OrderedAssocList.contains_insert, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.contains_insert.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {β : Type} {x : α}
        (l : Batteries.OrderedAssocList cmp β) (a : α) (b : β), Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) _ (Nat) (Bool.false) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
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

-- Batteries.OrderedAssocList.contains_insert, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.contains_insert.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] {β : Type} {x : α}
        (l : Batteries.OrderedAssocList cmp β) (a : α) (b : β), Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (Nat) (0) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) Nat }) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.LawfulLTCmp.eq_compareOfLessAndEq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.LawfulLTCmp.eq_compareOfLessAndEq.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : LT α] [inst_1 : DecidableEq α] [inst_2 : Std.LawfulEqCmp cmp] (x y : α)
        [inst_3 : Decidable (x < y)], cmp x y = compareOfLessAndEq x y := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (⟨fun a b => a ≤ b⟩ : LT Nat) (instDecidableEqNat) _ (0) (0) (Nat.decLe 0 0)) (by
  decide +kernel)

-- Substring.Raw.ValidFor.of_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.ValidFor.of_eq.h4 : ¬∀ {l m r : List Char} (s : Substring.Raw),
        s.startPos.byteIdx = String.utf8Len l →
          s.stopPos.byteIdx = String.utf8Len l + String.utf8Len m → Substring.Raw.ValidFor l m r s := fun hc_h => absurd (@hc_h ([]) ([]) ([]) ({ str := "a", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw }) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Substring.Raw.ValidFor.of_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.ValidFor.of_eq.h5 : ¬∀ {l m r : List Char} (s : Substring.Raw),
        s.str.toList = l ++ m ++ r →
          s.stopPos.byteIdx = String.utf8Len l + String.utf8Len m → Substring.Raw.ValidFor l m r s := fun hc_h => absurd (@hc_h ([]) ([]) ([]) ({ str := "", startPos := { byteIdx := 1 : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw }) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Substring.Raw.ValidFor.of_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.ValidFor.of_eq.h6 : ¬∀ {l m r : List Char} (s : Substring.Raw),
        s.str.toList = l ++ m ++ r → s.startPos.byteIdx = String.utf8Len l → Substring.Raw.ValidFor l m r s := fun hc_h => absurd (@hc_h ([]) (['a']) ([]) ({ str := "a", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw }) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- List.Nodup.perm_iff_eq_of_sublist, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.perm_iff_eq_of_sublist.h5 : ¬∀ {α : Type} {l₁ l₂ l : List α}, l.Nodup → l₂.Sublist l → (l₁.Perm l₂ ↔ l₁ = l₂) := fun hc_h => absurd (@hc_h (Nat) ([1, 0]) ([0, 1]) ([0, 1]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.perm_iff_eq_of_sublist, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.perm_iff_eq_of_sublist.h6 : ¬∀ {α : Type} {l₁ l₂ l : List α}, l.Nodup → l₁.Sublist l → (l₁.Perm l₂ ↔ l₁ = l₂) := fun hc_h => absurd (@hc_h (Nat) ([0, 1]) ([1, 0]) ([0, 1]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Batteries.AssocList.KeysOrdered.cons, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.KeysOrdered.cons.h6 : ¬∀ {α : Type} {a : α} {β : Type} {t : Batteries.AssocList α β} {b : β} {cmp : α → α → Ordering},
        Batteries.AssocList.KeysOrdered cmp t → Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons a b t) := fun hc_h => absurd (@hc_h (Nat) (0) (Nat) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) (0) (fun a b => compare a b : Nat → Nat → Ordering) (by
  decide)) (by
  decide +kernel)

-- Batteries.AssocList.KeysOrdered.cons, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.KeysOrdered.cons.h7 : ¬∀ {α : Type} {a : α} {β : Type} {t : Batteries.AssocList α β} {b : β} {cmp : α → α → Ordering},
        Batteries.AssocList.LTHeadKey cmp a t → Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons a b t) := fun hc_h => absurd (@hc_h (Nat) (0) (Bool) (Batteries.AssocList.cons 1 Bool.false (Batteries.AssocList.cons 0 Bool.false Batteries.AssocList.nil)) (Bool.false) (fun a b => compare a b : Nat → Nat → Ordering) (by
  decide)) (by
  decide +kernel)

-- Batteries.BinaryHeap.insertExtractMax_fst_of_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.insertExtractMax_fst_of_lt.h5 : ¬∀ {α : Type} {m x : α} [inst : Ord α] {heap : Batteries.BinaryHeap α},
        (Ord.compare x m).isLT = Bool.true → (heap.insertExtractMax x).fst = m := fun hc_h => absurd (@hc_h (Nat) (1) (0) (instOrdNat) ({ arr := #[] : Batteries.BinaryHeap Nat }) (by
  decide)) (by
  decide +kernel)

-- Batteries.BinaryHeap.insertExtractMax_fst_of_lt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.insertExtractMax_fst_of_lt.h6 : ¬∀ {α : Type} {m x : α} [inst : Ord α] {heap : Batteries.BinaryHeap α},
        heap.max = Option.some m → (heap.insertExtractMax x).fst = m := fun hc_h => absurd (@hc_h (Nat) (0) (1) (instOrdNat) ({ arr := #[0] : Batteries.BinaryHeap Nat }) (by
  decide)) (by
  decide +kernel)

-- ByteArray.get_append_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ByteArray.get_append_right.h3 : ¬∀ {i : Nat} {a b : ByteArray}, i < (a ++ b).size → a.size ≤ i := fun hc_h => absurd (@hc_h (0) ({ data := #[UInt8.ofNat 0] : ByteArray }) ({ data := #[] : ByteArray }) (by
  decide)) (by
  decide +kernel)

-- ByteArray.get_append_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ByteArray.get_append_right.h4 : ¬∀ {i : Nat} {a b : ByteArray}, a.size ≤ i → i < (a ++ b).size := fun hc_h => absurd (@hc_h (0) ({ data := #[] : ByteArray }) ({ data := #[] : ByteArray }) (by
  decide)) (by
  decide +kernel)

-- ByteArray.get_append_right, hypothesis 5: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.ByteArray.get_append_right.h5.der : ∀ {i : Nat} {a b : ByteArray},
      @LE.le Nat instLENat a.size i →
        @LT.lt Nat instLTNat i
            (@HAppend.hAppend ByteArray ByteArray ByteArray (@instHAppendOfAppend ByteArray ByteArray.instAppend) a
                b).size →
          @LT.lt Nat instLTNat (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) i a.size) b.size := by
  (intros; grind)
theorem HypCheckProof.ByteArray.get_append_right.h5 : ∀ {i : Nat} {a b : ByteArray} (hle : @LE.le Nat instLENat a.size i)
      (h :
        @LT.lt Nat instLTNat i
          (@HAppend.hAppend ByteArray ByteArray ByteArray (@instHAppendOfAppend ByteArray ByteArray.instAppend) a b).size),
      @Eq UInt8
        (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
          ByteArray.instGetElemNatUInt8LtSize
          (@HAppend.hAppend ByteArray ByteArray ByteArray (@instHAppendOfAppend ByteArray ByteArray.instAppend) a b) i h)
        (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
          ByteArray.instGetElemNatUInt8LtSize b (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) i a.size)
          (@HypCheckProof.ByteArray.get_append_right.h5.der i a b hle h)) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @ByteArray.get_append_right hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.ByteArray.get_append_right.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4)

-- List.Perm.interleave, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.interleave.h5 : ¬∀ {α : Type} {l₁ l₃ l₂ l₄ : List α}, l₂.Perm l₄ → (l₁.interleave l₂).Perm (l₃.interleave l₄) := fun hc_h => absurd (@hc_h (Nat) ([]) ([0]) ([]) ([]) (by
  decide)) (by
  decide +kernel)

-- List.Perm.interleave, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.interleave.h6 : ¬∀ {α : Type} {l₁ l₃ l₂ l₄ : List α}, l₁.Perm l₃ → (l₁.interleave l₂).Perm (l₃.interleave l₄) := fun hc_h => absurd (@hc_h (Nat) ([]) ([]) ([]) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.coe_idxInj, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.coe_idxInj.h2 : ¬∀ {α : Type} [inst : BEq α] {xs ys : List α} {h : xs.Subperm ys} {i : Fin xs.length}, ReflBEq α := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a != b⟩ : BEq Nat) ([0]) ([0]) (by
  decide) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  exact fun hc_c =>
    absurd (hc_c.rfl (a := (0 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.coe_idxInj, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.coe_idxInj.h5 : ¬∀ {α : Type} [inst : BEq α] [inst : ReflBEq α] {xs ys : List α} {i : Fin xs.length}, xs.Subperm ys := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([0]) ([]) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.Perm.coe_idxBij, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.coe_idxBij.h2 : ¬∀ {α : Type} [inst : BEq α] {xs ys : List α}, xs.Perm ys → ∀ {i : Fin xs.length}, ReflBEq α := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a != b⟩ : BEq Nat) ([0]) ([0]) (by
  decide) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  exact fun hc_c =>
    absurd (hc_c.rfl (a := (0 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.Perm.coe_idxBij, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.coe_idxBij.h5 : ¬∀ {α : Type} [inst : BEq α] [inst : ReflBEq α] {xs ys : List α} {i : Fin xs.length}, xs.Perm ys := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([0]) ([]) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.Perm.diff_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.diff_left.h6 : ¬∀ {α : Type} {t₁ t₂ : List α} [inst : BEq α] [inst_1 : LawfulBEq α] (l : List α), l.diff t₁ = l.diff t₂ := fun hc_h => absurd (@hc_h (Nat) ([]) ([0]) (instBEqOfDecidableEq) _ ([0])) (by
  decide +kernel)

-- List.Perm.getElem_idxBij_eq_getElem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.getElem_idxBij_eq_getElem.h2 : ¬∀ {α : Type} [inst : BEq α] {xs ys : List α}, xs.Perm ys → ∀ (i : Fin xs.length), LawfulBEq α := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([0]) ([0]) (by
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

-- List.Perm.getElem_idxBij_eq_getElem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.getElem_idxBij_eq_getElem.h5 : ¬∀ {α : Type} [inst : BEq α] [inst : LawfulBEq α] {xs ys : List α} (i : Fin xs.length), xs.Perm ys := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([0]) ([]) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.Perm.idxBij_idxBij_symm, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.idxBij_idxBij_symm.h2 : ¬∀ {α : Type} [inst : BEq α] {xs ys : List α}, xs.Perm ys → ∀ {i : Fin ys.length}, LawfulBEq α := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([0]) ([0]) (by
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

-- List.Perm.idxBij_idxBij_symm, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.idxBij_idxBij_symm.h5 : ¬∀ {α : Type} [inst : BEq α] [inst : LawfulBEq α] {xs ys : List α} {i : Fin ys.length}, xs.Perm ys := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([]) ([0]) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.cons_diff_of_mem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.cons_diff_of_mem.h2 : ¬∀ {α : Type} [inst : BEq α] {a : α} {l₂ : List α}, a ∈ l₂ → ∀ (l₁ : List α), (a :: l₁).diff l₂ = l₁.diff (l₂.erase a) := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a != b⟩ : BEq Nat) (0) ([0]) (by
  decide) ([])) (by
  decide +kernel)

-- List.cons_diff_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.cons_diff_of_mem.h5 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : LawfulBEq α] {a : α} {l₂ : List α} (l₁ : List α),
        (a :: l₁).diff l₂ = l₁.diff (l₂.erase a) := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ (0) ([]) ([])) (by
  decide +kernel)

-- List.cons_diff_of_not_mem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.cons_diff_of_not_mem.h2 : ¬∀ {α : Type} [inst : BEq α] {a : α} {l₂ : List α}, ¬a ∈ l₂ → ∀ (l₁ : List α), (a :: l₁).diff l₂ = a :: l₁.diff l₂ := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (0) ([1]) (by
  decide) ([])) (by
  decide +kernel)

-- List.cons_diff_of_not_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.cons_diff_of_not_mem.h5 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : LawfulBEq α] {a : α} {l₂ : List α} (l₁ : List α),
        (a :: l₁).diff l₂ = a :: l₁.diff l₂ := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ (0) ([0]) ([])) (by
  decide +kernel)

-- Nat.bisect_lt_stop, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.bisect_lt_stop.h3.inst : ¬2 < 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.bisect_lt_stop.h3.prem0 : (fun (n : Nat) => n % 2 == 0) 2 = Bool.true := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.bisect_lt_stop.h3.prem1 : (fun (n : Nat) => n % 2 == 0) 1 = Bool.false := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Nat.bisect_lt_stop.h3 : ¬∀ {start stop : Nat} {p : Nat → Bool}, p start = Bool.true → p stop = Bool.false → start < stop := fun hc_h => HypCheckProof.Nat.bisect_lt_stop.h3.inst (@hc_h (2) (1) (fun (n : Nat) => n % 2 == 0) HypCheckProof.Nat.bisect_lt_stop.h3.prem0 HypCheckProof.Nat.bisect_lt_stop.h3.prem1)

-- Nat.bisect_lt_stop, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.bisect_lt_stop.h4 : ¬∀ {start stop : Nat} {p : Nat → Bool}, start < stop → p stop = Bool.false → p start = Bool.true := fun hc_h => absurd (@hc_h (0) (1) (fun _ => false : Nat → Bool) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Nat.bisect_lt_stop, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.bisect_lt_stop.h5.inst : ¬(fun (n : Nat) => n % 2 == 0) 2 = Bool.false := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.bisect_lt_stop.h5.prem0 : 0 < 2 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.bisect_lt_stop.h5.prem1 : (fun (n : Nat) => n % 2 == 0) 0 = Bool.true := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Nat.bisect_lt_stop.h5 : ¬∀ {start stop : Nat} {p : Nat → Bool}, start < stop → p start = Bool.true → p stop = Bool.false := fun hc_h => HypCheckProof.Nat.bisect_lt_stop.h5.inst (@hc_h (0) (2) (fun (n : Nat) => n % 2 == 0) HypCheckProof.Nat.bisect_lt_stop.h5.prem0 HypCheckProof.Nat.bisect_lt_stop.h5.prem1)

-- Nat.bisect_true, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.bisect_true.h3.inst : ¬2 < 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.bisect_true.h3.prem0 : (fun (n : Nat) => n % 2 == 0) 2 = Bool.true := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.bisect_true.h3.prem1 : (fun (n : Nat) => n % 2 == 0) 1 = Bool.false := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Nat.bisect_true.h3 : ¬∀ {start stop : Nat} {p : Nat → Bool}, p start = Bool.true → p stop = Bool.false → start < stop := fun hc_h => HypCheckProof.Nat.bisect_true.h3.inst (@hc_h (2) (1) (fun (n : Nat) => n % 2 == 0) HypCheckProof.Nat.bisect_true.h3.prem0 HypCheckProof.Nat.bisect_true.h3.prem1)

-- Nat.bisect_true, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.bisect_true.h4 : ¬∀ {start stop : Nat} {p : Nat → Bool}, start < stop → p stop = Bool.false → p start = Bool.true := fun hc_h => absurd (@hc_h (0) (1) (fun _ => false : Nat → Bool) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Nat.bisect_true, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.bisect_true.h5.inst : ¬(fun (n : Nat) => n % 2 == 0) 2 = Bool.false := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.bisect_true.h5.prem0 : 0 < 2 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.bisect_true.h5.prem1 : (fun (n : Nat) => n % 2 == 0) 0 = Bool.true := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Nat.bisect_true.h5 : ¬∀ {start stop : Nat} {p : Nat → Bool}, start < stop → p start = Bool.true → p stop = Bool.false := fun hc_h => HypCheckProof.Nat.bisect_true.h5.inst (@hc_h (0) (2) (fun (n : Nat) => n % 2 == 0) HypCheckProof.Nat.bisect_true.h5.prem0 HypCheckProof.Nat.bisect_true.h5.prem1)

-- Nat.start_le_bisect, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.start_le_bisect.h3.inst : ¬2 < 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.start_le_bisect.h3.prem0 : (fun (n : Nat) => n % 2 == 0) 2 = Bool.true := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.start_le_bisect.h3.prem1 : (fun (n : Nat) => n % 2 == 0) 1 = Bool.false := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Nat.start_le_bisect.h3 : ¬∀ {start stop : Nat} {p : Nat → Bool}, p start = Bool.true → p stop = Bool.false → start < stop := fun hc_h => HypCheckProof.Nat.start_le_bisect.h3.inst (@hc_h (2) (1) (fun (n : Nat) => n % 2 == 0) HypCheckProof.Nat.start_le_bisect.h3.prem0 HypCheckProof.Nat.start_le_bisect.h3.prem1)

-- Nat.start_le_bisect, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.start_le_bisect.h4 : ¬∀ {start stop : Nat} {p : Nat → Bool}, start < stop → p stop = Bool.false → p start = Bool.true := fun hc_h => absurd (@hc_h (0) (1) (fun _ => false : Nat → Bool) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Nat.start_le_bisect, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.start_le_bisect.h5.inst : ¬(fun (n : Nat) => n % 2 == 0) 2 = Bool.false := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.start_le_bisect.h5.prem0 : 0 < 2 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.start_le_bisect.h5.prem1 : (fun (n : Nat) => n % 2 == 0) 0 = Bool.true := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Nat.start_le_bisect.h5 : ¬∀ {start stop : Nat} {p : Nat → Bool}, start < stop → p start = Bool.true → p stop = Bool.false := fun hc_h => HypCheckProof.Nat.start_le_bisect.h5.inst (@hc_h (0) (2) (fun (n : Nat) => n % 2 == 0) HypCheckProof.Nat.start_le_bisect.h5.prem0 HypCheckProof.Nat.start_le_bisect.h5.prem1)

-- Nat.bisect_add_one_false, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.bisect_add_one_false.h3.inst : ¬2 < 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.bisect_add_one_false.h3.prem0 : (fun (n : Nat) => n % 2 == 0) 2 = Bool.true := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.bisect_add_one_false.h3.prem1 : (fun (n : Nat) => n % 2 == 0) 1 = Bool.false := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Nat.bisect_add_one_false.h3 : ¬∀ {start stop : Nat} {p : Nat → Bool}, p start = Bool.true → p stop = Bool.false → start < stop := fun hc_h => HypCheckProof.Nat.bisect_add_one_false.h3.inst (@hc_h (2) (1) (fun (n : Nat) => n % 2 == 0) HypCheckProof.Nat.bisect_add_one_false.h3.prem0 HypCheckProof.Nat.bisect_add_one_false.h3.prem1)

-- Nat.bisect_add_one_false, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.bisect_add_one_false.h4 : ¬∀ {start stop : Nat} {p : Nat → Bool}, start < stop → p stop = Bool.false → p start = Bool.true := fun hc_h => absurd (@hc_h (0) (1) (fun _ => false : Nat → Bool) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Nat.bisect_add_one_false, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.bisect_add_one_false.h5.inst : ¬(fun (n : Nat) => n % 2 == 0) 2 = Bool.false := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.bisect_add_one_false.h5.prem0 : 0 < 2 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.bisect_add_one_false.h5.prem1 : (fun (n : Nat) => n % 2 == 0) 0 = Bool.true := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Nat.bisect_add_one_false.h5 : ¬∀ {start stop : Nat} {p : Nat → Bool}, start < stop → p start = Bool.true → p stop = Bool.false := fun hc_h => HypCheckProof.Nat.bisect_add_one_false.h5.inst (@hc_h (0) (2) (fun (n : Nat) => n % 2 == 0) HypCheckProof.Nat.bisect_add_one_false.h5.prem0 HypCheckProof.Nat.bisect_add_one_false.h5.prem1)

-- Nat.toFinDigits_eq_append, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.toFinDigits_eq_append.h3 : ¬∀ {base k n : Nat} [inst : NeZero base],
        base ^ k ≤ n → n.toFinDigits base = (n / base ^ k).toFinDigits base ++ (n % base ^ k).toFinDigitsFixed base k := fun hc_h => absurd (@hc_h (1) (1) (1) _ (by
  decide)) (by
  decide +kernel)

-- Nat.toFinDigits_eq_append, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.toFinDigits_eq_append.h5 : ¬∀ {base k n : Nat},
        2 ≤ base →
          ∀ [inst : NeZero base],
            n.toFinDigits base = (n / base ^ k).toFinDigits base ++ (n % base ^ k).toFinDigitsFixed base k := fun hc_h => absurd (@hc_h (2) (1) (0) (by
  decide) _) (by
  decide +kernel)

-- List.exists_of_replaceF, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.exists_of_replaceF.h5 : ¬∀ {α : Type} {p : α → Option α} {l : List α} {a a' : α},
        p a = Option.some a' →
          ∃ (a : α),
            ∃ (a' : α),
              ∃ (l₁ : List α),
                ∃ (l₂ : List α),
                  (∀ (b : α), b ∈ l₁ → p b = Option.none) ∧
                    p a = Option.some a' ∧ l = l₁ ++ a :: l₂ ∧ List.replaceF p l = l₁ ++ a' :: l₂ := fun hc_h => absurd (@hc_h (Nat) (some : Nat → Option Nat) ([]) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  simp)

-- List.exists_of_replaceF, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.exists_of_replaceF.h6 : ¬∀ {α : Type} {p : α → Option α} {l : List α} {a : α} {a' : α},
        a ∈ l →
          ∃ (a : α),
            ∃ (a' : α),
              ∃ (l₁ : List α),
                ∃ (l₂ : List α),
                  (∀ (b : α), b ∈ l₁ → p b = Option.none) ∧
                    p a = Option.some a' ∧ l = l₁ ++ a :: l₂ ∧ List.replaceF p l = l₁ ++ a' :: l₂ := fun hc_h => absurd (@hc_h (Nat) (fun _ => none : Nat → Option Nat) ([0]) (0) (0) (by
  decide)) (by
  simp)

-- List.IsChain.cons_of_imp, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.cons_of_imp.h5 : ¬∀ {α : Type} {R : α → α → Prop} {a : α} {l : List α} {b : α}, List.IsChain R (a :: l) → List.IsChain R (b :: l) := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (0) ([1]) (1) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.cons_of_imp, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.cons_of_imp.h6 : ¬∀ {α : Type} {R : α → α → Prop} {a : α} {l : List α} {b : α}, (∀ (c : α), R a c → R b c) → List.IsChain R (b :: l) := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (0) ([0]) (0) (by
  simp)) (by
  decide +kernel)

-- List.countBefore_lt_count_of_lt_length_of_beq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.countBefore_lt_count_of_lt_length_of_beq.h5 : ¬∀ {α : Type} {i : Nat} {x : α} [inst : BEq α] {xs : List α}, i < xs.length := fun hc_h => absurd (@hc_h (Nat) (0) (0) (instBEqOfDecidableEq) ([])) (by
  decide +kernel)

-- List.countBefore_lt_count_of_lt_length_of_beq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.countBefore_lt_count_of_lt_length_of_beq.h6 : ¬∀ {α : Type} {i : Nat} {x : α} [inst : BEq α] {xs : List α} {h : i < xs.length},
        List.countBefore x xs i < List.count x xs := fun hc_h => absurd (@hc_h (Nat) (0) (0) (instBEqOfDecidableEq) ([1]) (by
  decide)) (by
  decide +kernel)

-- List.append_eq_of_isSuffixOf?_eq_some, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.append_eq_of_isSuffixOf?_eq_some.h2 : ¬∀ {α : Type} [inst : BEq α] {xs ys zs : List α}, xs.isSuffixOf? ys = Option.some zs → zs ++ xs = ys := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([0]) ([1]) ([]) (by
  decide)) (by
  decide +kernel)

-- List.append_eq_of_isSuffixOf?_eq_some, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.append_eq_of_isSuffixOf?_eq_some.h6 : ¬∀ {α : Type} [inst : BEq α] [inst : LawfulBEq α] {xs ys zs : List α}, zs ++ xs = ys := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([]) ([]) ([0])) (by
  decide +kernel)

-- Batteries.PairingHeapImp.Heap.size_deleteMin, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.PairingHeapImp.Heap.size_deleteMin.h5 : ¬∀ {α : Type} {le : α → α → Bool} {a : α} {s' s : Batteries.PairingHeapImp.Heap α},
        Batteries.PairingHeapImp.Heap.deleteMin le s = Option.some (a, s') → s.size = s'.size + 1 := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Bool) (0) (Batteries.PairingHeapImp.Heap.nil) (Batteries.PairingHeapImp.Heap.node 0 Batteries.PairingHeapImp.Heap.nil
      (Batteries.PairingHeapImp.Heap.node 0 Batteries.PairingHeapImp.Heap.nil Batteries.PairingHeapImp.Heap.nil)) (by
  rfl)) (by
  decide +kernel)

-- Batteries.PairingHeapImp.Heap.size_deleteMin, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.PairingHeapImp.Heap.size_deleteMin.h6 : ¬∀ {α : Type} {le : α → α → Bool} {a : α} {s' s : Batteries.PairingHeapImp.Heap α}, s.NoSibling → s.size = s'.size + 1 := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Bool) (0) (Batteries.PairingHeapImp.Heap.nil) (Batteries.PairingHeapImp.Heap.nil) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.cons_of_imp_of_cons, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.cons_of_imp_of_cons.h5 : ¬∀ {α : Type} {R : α → α → Prop} {a : α} {l : List α} {b : α}, List.IsChain R (a :: l) → List.IsChain R (b :: l) := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (0) ([1]) (1) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.cons_of_imp_of_cons, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.cons_of_imp_of_cons.h6 : ¬∀ {α : Type} {R : α → α → Prop} {a : α} {l : List α} {b : α}, (∀ (c : α), R a c → R b c) → List.IsChain R (b :: l) := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (0) ([0]) (0) (by
  simp)) (by
  decide +kernel)

-- List.getElem_getElem_idxsOf_of_lawful, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_getElem_idxsOf_of_lawful.h5 : ¬∀ {α : Type} {i : Nat} {xs : List α} {x : α} [inst : BEq α] (h : i < (List.idxsOf x xs).length),
        GetElem.getElem xs (GetElem.getElem (List.idxsOf x xs) i h) (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) = x := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (0) ([0]) (1) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) hc_k0) (by
  decide +kernel)

-- List.getElem_getElem_idxsOf_of_lawful, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_getElem_idxsOf_of_lawful.h6 : ¬∀ {α : Type} {i : Nat} {xs : List α} {x : α} [inst : BEq α] [inst_1 : LawfulBEq α], i < (List.idxsOf x xs).length := fun hc_h => absurd (@hc_h (Nat) (0) ([]) (0) (instBEqOfDecidableEq) _) (by
  decide +kernel)

-- List.getElem_idxOfNth_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_idxOfNth_eq.h5 : ¬∀ {α : Type} {x : α} {n : Nat} {xs : List α} [inst : BEq α] {h : List.idxOfNth x xs n < xs.length},
        xs[List.idxOfNth x xs n] = x := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (0) (0) ([1]) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) hc_k0) (by
  decide +kernel)

-- List.getElem_idxOfNth_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_idxOfNth_eq.h6 : ¬∀ {α : Type} {x : α} {n : Nat} {xs : List α} [inst : BEq α] [inst_1 : LawfulBEq α], List.idxOfNth x xs n < xs.length := fun hc_h => absurd (@hc_h (Nat) (0) (0) ([]) (instBEqOfDecidableEq) _) (by
  decide +kernel)

-- Batteries.BinaryHeap.insertExtractMax_fst_of_not_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.insertExtractMax_fst_of_not_lt.h5 : ¬∀ {α : Type} {m x : α} [inst : Ord α] {heap : Batteries.BinaryHeap α},
        ¬(Ord.compare x m).isLT = Bool.true → (heap.insertExtractMax x).fst = x := fun hc_h => absurd (@hc_h (Nat) (0) (0) (instOrdNat) ({ arr := #[1] : Batteries.BinaryHeap Nat }) (by
  decide)) (by
  decide +kernel)

-- Batteries.BinaryHeap.insertExtractMax_fst_of_not_lt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.insertExtractMax_fst_of_not_lt.h6 : ¬∀ {α : Type} {m x : α} [inst : Ord α] {heap : Batteries.BinaryHeap α},
        heap.max = Option.some m → (heap.insertExtractMax x).fst = x := fun hc_h => absurd (@hc_h (Nat) (1) (0) (instOrdNat) ({ arr := #[1] : Batteries.BinaryHeap Nat }) (by
  decide)) (by
  decide +kernel)

-- String.Legacy.Iterator.ValidFor.extract, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Legacy.Iterator.ValidFor.extract.h5 : ¬∀ {l m r : List Char} {it₁ it₂ : String.Legacy.Iterator},
        String.Legacy.Iterator.ValidFor (m.reverse ++ l) r it₂ → it₁.extract it₂ = String.ofList m := fun hc_h => absurd (@hc_h ([]) (['a']) ([]) ({ s := "", i := { : String.Pos.Raw } : String.Legacy.Iterator }) ({ s := "a", i := { byteIdx := 1 : String.Pos.Raw } : String.Legacy.Iterator }) (by
  decide)) (by
  decide +kernel)

-- String.Legacy.Iterator.ValidFor.extract, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Legacy.Iterator.ValidFor.extract.h6 : ¬∀ {l m r : List Char} {it₁ it₂ : String.Legacy.Iterator},
        String.Legacy.Iterator.ValidFor l (m ++ r) it₁ → it₁.extract it₂ = String.ofList m := fun hc_h => absurd (@hc_h ([]) (['a']) ([]) ({ s := "a", i := { : String.Pos.Raw } : String.Legacy.Iterator }) ({ s := "", i := { : String.Pos.Raw } : String.Legacy.Iterator }) (by
  decide)) (by
  decide +kernel)

-- Eq.congr, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Eq.congr.h5 : ¬∀ {α : Type} {x₁ y₁ x₂ y₂ : α}, x₂ = y₂ → (x₁ = x₂ ↔ y₁ = y₂) := fun hc_h => absurd (@hc_h (Nat) (0) (1) _ (0) rfl) (by
  decide +kernel)

-- Eq.congr, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Eq.congr.h6 : ¬∀ {α : Type} {x₁ y₁ x₂ y₂ : α}, x₁ = y₁ → (x₁ = x₂ ↔ y₁ = y₂) := fun hc_h => absurd (@hc_h (Nat) _ (0) (0) (1) rfl) (by
  decide +kernel)

-- List.Subperm.idxInj_injective, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.idxInj_injective.h2 : ¬∀ {α : Type} [inst : BEq α] {xs ys : List α}, xs.Subperm ys → LawfulBEq α := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([]) ([]) (by
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

-- List.Subperm.idxInj_injective, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.idxInj_injective.h5 : ¬∀ {α : Type} [inst : BEq α] [inst : LawfulBEq α] {xs ys : List α}, xs.Subperm ys := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([0]) ([])) (by
  decide +kernel)

-- String.Legacy.Iterator.ValidFor.prevn, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Legacy.Iterator.ValidFor.prevn.h3 : ¬∀ {l r : List Char} {it : String.Legacy.Iterator} (n : Nat),
        n ≤ l.length → String.Legacy.Iterator.ValidFor (List.drop n l) ((List.take n l).reverse ++ r) (it.prevn n) := fun hc_h => absurd (@hc_h ([]) ([]) ({ s := "", i := { byteIdx := 1 : String.Pos.Raw } : String.Legacy.Iterator }) (0) (by
  decide)) (by
  decide +kernel)

-- heq_of_cast_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.heq_of_cast_eq.h5 : ¬∀ {α β : Type} {a : α} {a' : β}, α = β → a ≍ a' := fun hc_h => absurd (@hc_h (Nat) (Nat) (0) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  simp)

-- Vector.toList_scanrM, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.toList_scanrM.h6 : ¬∀ {m : Type → Type} {α β : Type} {n : Nat} {init : β} [inst : Monad m] {f : α → β → m β} {as : Vector α n},
        Vector.toList <$> Vector.scanrM f init as = List.scanrM f init as.toList := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) (0) (0) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 : Nat) => (0, 0)) (#v[])) (by
  decide +kernel)

-- ForInStep.bindList_append, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.ForInStep.bindList_append.h4.inst : Not
      (@Eq (Option (ForInStep Nat))
        (@ForInStep.bindList Option Nat Nat
          (@Monad.mk Option
            (@Applicative.mk Option instFunctorOption (@Pure.mk Option fun {α : Type} => @Option.some α)
              (@Applicative.toSeq Option (@Alternative.toApplicative Option instAlternativeOption))
              (@Applicative.toSeqLeft Option (@Alternative.toApplicative Option instAlternativeOption))
              (@Applicative.toSeqRight Option (@Alternative.toApplicative Option instAlternativeOption)))
            (@Bind.mk Option fun {α β : Type} (x : Option α) (x_1 : α → Option β) => @Option.none β))
          (fun (a a_1 : Nat) => @Option.none (ForInStep Nat))
          (@HAppend.hAppend (List Nat) (List Nat) (List Nat) (@instHAppendOfAppend (List Nat) (@List.instAppend Nat))
            (@List.nil Nat) (@List.nil Nat))
          (@ForInStep.yield Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Option.none (ForInStep Nat))) := by
  decide +kernel
theorem HypCheckProof.ForInStep.bindList_append.h4 : Not
      (∀ {m : Type → Type} {α β : Type} [inst : Monad m] (f : α → β → m (ForInStep β)) (s : ForInStep β) (l₁ l₂ : List α),
        @Eq (m (ForInStep β))
          (@ForInStep.bindList m α β inst f
            (@HAppend.hAppend (List α) (List α) (List α) (@instHAppendOfAppend (List α) (@List.instAppend α)) l₁ l₂) s)
          (@Bind.bind m (@Monad.toBind m inst) (ForInStep β) (ForInStep β) (@ForInStep.bindList m α β inst f l₁ s)
            fun (x : ForInStep β) => @ForInStep.bindList m α β inst f l₂ x)) := fun hc_h => HypCheckProof.ForInStep.bindList_append.h4.inst (@hc_h (Option) (Nat) (Nat) (@Monad.mk Option
      (@Applicative.mk Option instFunctorOption (@Pure.mk Option fun {α : Type} => @Option.some α)
        (@Applicative.toSeq Option (@Alternative.toApplicative Option instAlternativeOption))
        (@Applicative.toSeqLeft Option (@Alternative.toApplicative Option instAlternativeOption))
        (@Applicative.toSeqRight Option (@Alternative.toApplicative Option instAlternativeOption)))
      (@Bind.mk Option fun {α β : Type} (x : Option α) (x_1 : α → Option β) => @Option.none β)) (fun (a a_1 : Nat) => @Option.none (ForInStep Nat)) (@ForInStep.yield Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@List.nil Nat) (@List.nil Nat))

-- Nat.toFinDigits_of_ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.toFinDigits_of_ne_zero.h2 : ¬∀ {base n : Nat} [inst : NeZero base], n ≠ 0 → n.toFinDigits base = (n / base).toFinDigits base ++ [Fin.ofNat base n] := fun hc_h => absurd (@hc_h (1) (1) _ (by
  decide)) (by
  decide +kernel)

-- Nat.toFinDigits_of_ne_zero, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.toFinDigits_of_ne_zero.h4 : ¬∀ {base n : Nat},
        2 ≤ base → ∀ [inst : NeZero base], n.toFinDigits base = (n / base).toFinDigits base ++ [Fin.ofNat base n] := fun hc_h => absurd (@hc_h (2) (0) (by
  decide) _) (by
  decide +kernel)

-- ForInStep.bind_bindList_assoc, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.ForInStep.bind_bindList_assoc.h4.inst : Not
      (@Eq (Option (ForInStep Nat)) (@Option.none (ForInStep Nat))
        (@ForInStep.bind Option Nat
          (@Monad.mk Option
            (@Applicative.mk Option instFunctorOption (@Pure.mk Option fun {α : Type} => @Option.some α)
              (@Applicative.toSeq Option (@Alternative.toApplicative Option instAlternativeOption))
              (@Applicative.toSeqLeft Option (@Alternative.toApplicative Option instAlternativeOption))
              (@Applicative.toSeqRight Option (@Alternative.toApplicative Option instAlternativeOption)))
            (@Bind.mk Option fun {α β : Type} (x : Option α) (x_1 : α → Option β) => @Option.none β))
          (@ForInStep.done Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) fun (b : Nat) =>
          @Option.none (ForInStep Nat))) := by
  decide +kernel
theorem HypCheckProof.ForInStep.bind_bindList_assoc.h4 : Not
      (∀ {m : Type → Type} {β α : Type} [inst : Monad m] (f : β → m (ForInStep β)) (g : α → β → m (ForInStep β))
        (s : ForInStep β) (l : List α),
        @Eq (m (ForInStep β))
          (@Bind.bind m (@Monad.toBind m inst) (ForInStep β) (ForInStep β) (@ForInStep.bind m β inst s f)
            fun (x : ForInStep β) => @ForInStep.bindList m α β inst g l x)
          (@ForInStep.bind m β inst s fun (b : β) =>
            @Bind.bind m (@Monad.toBind m inst) (ForInStep β) (ForInStep β) (f b) fun (x : ForInStep β) =>
              @ForInStep.bindList m α β inst g l x)) := fun hc_h => HypCheckProof.ForInStep.bind_bindList_assoc.h4.inst (@hc_h (Option) (Nat) (Nat) (@Monad.mk Option
      (@Applicative.mk Option instFunctorOption (@Pure.mk Option fun {α : Type} => @Option.some α)
        (@Applicative.toSeq Option (@Alternative.toApplicative Option instAlternativeOption))
        (@Applicative.toSeqLeft Option (@Alternative.toApplicative Option instAlternativeOption))
        (@Applicative.toSeqRight Option (@Alternative.toApplicative Option instAlternativeOption)))
      (@Bind.mk Option fun {α β : Type} (x : Option α) (x_1 : α → Option β) => @Option.none β)) (fun (a : Nat) => @Option.none (ForInStep Nat)) (fun (a a_1 : Nat) => @Option.none (ForInStep Nat)) (@ForInStep.done Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@List.nil Nat))

-- Array.scanrM_eq_scanrM_toList, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.scanrM_eq_scanrM_toList.h5 : ¬∀ {m : Type → Type} {α β : Type} {init : β} [inst : Monad m] {f : α → β → m β} {as : Array α},
        Array.scanrM f init as = List.toArray <$> List.scanrM f init as.toList := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) (0) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 : Nat) => (0, 0)) (#[])) (by
  decide +kernel)

-- Array.scanlM_reverse, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.scanlM_reverse.h5 : ¬∀ {m : Type → Type} {β α : Type} {init : β} [inst : Monad m] {f : β → α → m β} {as : Array α},
        Array.scanlM f init as.reverse = Array.reverse <$> Array.scanrM (flip f) init as := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) (0) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 : Nat) => (0, 0)) (#[])) (by
  decide +kernel)

-- List.Subperm.perm_of_length_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.perm_of_length_le.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₂.length ≤ l₁.length → l₁.Perm l₂ := fun hc_h => absurd (@hc_h (Nat) ([0]) ([]) (by
  decide)) (by
  decide +kernel)

-- List.Subperm.perm_of_length_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.perm_of_length_le.h4 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁.Subperm l₂ → l₁.Perm l₂ := fun hc_h => absurd (@hc_h (Nat) ([]) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.subperm_of_subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.subperm_of_subset.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁ ⊆ l₂ → l₁.Subperm l₂ := fun hc_h => absurd (@hc_h (Nat) ([0, 0]) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.subperm_of_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.subperm_of_subset.h4 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁.Nodup → l₁.Subperm l₂ := fun hc_h => absurd (@hc_h (Nat) ([0]) ([]) (by
  decide)) (by
  decide +kernel)

-- String.Legacy.Iterator.ValidFor.of_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Legacy.Iterator.ValidFor.of_eq.h3 : ¬∀ {l r : List Char} (it : String.Legacy.Iterator),
        it.i.byteIdx = String.utf8Len l → String.Legacy.Iterator.ValidFor l r it := fun hc_h => absurd (@hc_h ([]) (['a']) ({ s := "", i := { : String.Pos.Raw } : String.Legacy.Iterator }) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- String.Legacy.Iterator.ValidFor.of_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Legacy.Iterator.ValidFor.of_eq.h4 : ¬∀ {l r : List Char} (it : String.Legacy.Iterator),
        it.s.toList = l.reverseAux r → String.Legacy.Iterator.ValidFor l r it := fun hc_h => absurd (@hc_h ([]) ([]) ({ s := "", i := { byteIdx := 1 : String.Pos.Raw } : String.Legacy.Iterator }) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Std.LawfulBCmp.eq_lt_iff_lt, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulBCmp.eq_lt_iff_lt.h5.inst : ¬((fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.lt ↔ 0 ≤ 0) := by
  decide +kernel
theorem HypCheckProof.Std.LawfulBCmp.eq_lt_iff_lt.h5 : ¬∀ {α : Type} {inst : LE α} {inst : LT α} {inst_1 : BEq α} {cmp : α → α → Ordering} {x y : α},
        cmp x y = Ordering.lt ↔ x < y := fun hc_h => HypCheckProof.Std.LawfulBCmp.eq_lt_iff_lt.h5.inst (@hc_h (Nat) (instLENat) ({ lt := fun (a b : Nat) => a ≤ b : LT Nat }) (instBEqOfDecidableEq) (fun (a b : Nat) => Ord.compare a b) (0) (0))

-- Substring.Raw.Valid.front, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.Valid.front.h4 : ¬∀ {c : Char} {m : List Char} {s : Substring.Raw}, s.Valid → s.front = c := fun hc_h => absurd (@hc_h ('a') ([]) ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw }) ((@Substring.Raw.Valid.mk ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw }) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   decide)))) (by
  decide +kernel)

-- List.rel_of_isChain_cons_cons, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.rel_of_isChain_cons_cons.h5 : ¬∀ {α : Type} {R : α → α → Prop} {a b : α} {l : List α}, R a b := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (0) (0) ([])) (by
  decide +kernel)

-- Std.LawfulBCmp.toLawfulLECmp, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.LawfulBCmp.toLawfulLECmp.h5 : ¬∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : BEq α] {cmp : α → α → Ordering}, Std.LawfulLECmp cmp := fun hc_h => absurd (@hc_h (Nat) (instLENat) (instLTNat) (instBEqOfDecidableEq) (fun a b => compare (a / 2) (b / 2) : Nat → Nat → Ordering)) (by
  exact fun hc_c =>
    absurd (hc_c.isLE_iff_le (x := (1 : Nat)) (y := (0 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.cons_diff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.cons_diff.h2 : ¬∀ {α : Type} [inst : BEq α] (a : α) (l₁ l₂ : List α), LawfulBEq α := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (0) ([]) ([])) (by
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

-- Std.LawfulLECmp.isGE_iff_ge, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.LawfulLECmp.isGE_iff_ge.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {x y : α} [inst : LE α], (cmp x y).isGE = Bool.true ↔ y ≤ x := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare (a / 2) (b / 2) : Nat → Nat → Ordering) (0) (1) (instLENat)) (by
  decide +kernel)

-- List.countPBefore_cons_succ_of_neg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.countPBefore_cons_succ_of_neg.h5 : ¬∀ {α : Type} {p : α → Bool} {xs : List α} {i : Nat} {a : α},
        List.countPBefore p (a :: xs) (i + 1) = List.countPBefore p xs i := fun hc_h => absurd (@hc_h (Nat) (fun n => n % 2 == 0 : Nat → Bool) ([]) (0) (0)) (by
  decide +kernel)

-- List.findIdxNth_eq_findIdxNth_iff_of_right_lt_countP, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.findIdxNth_eq_findIdxNth_iff_of_right_lt_countP.h5 : ¬∀ {α : Type} {m : Nat} {p : α → Bool} {n : Nat} {xs : List α}, List.findIdxNth p xs n = List.findIdxNth p xs m ↔ n = m := fun hc_h => absurd (@hc_h (Nat) (0) (fun n => n % 2 == 0 : Nat → Bool) (1) ([])) (by
  decide +kernel)

-- List.isSuffixOf?_eq_some_iff_append_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.isSuffixOf?_eq_some_iff_append_eq.h2 : ¬∀ {α : Type} [inst : BEq α] {xs ys zs : List α}, xs.isSuffixOf? ys = Option.some zs ↔ zs ++ xs = ys := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([0]) ([1]) ([])) (by
  decide +kernel)

-- Batteries.PairingHeapImp.Heap.noSibling_deleteMin, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.PairingHeapImp.Heap.noSibling_deleteMin.h5 : ¬∀ {α : Type} {le : α → α → Bool} {a : α} {s' : Batteries.PairingHeapImp.Heap α} {s : Batteries.PairingHeapImp.Heap α},
        s'.NoSibling := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Bool) (0) (Batteries.PairingHeapImp.Heap.node 0 Batteries.PairingHeapImp.Heap.nil
      (Batteries.PairingHeapImp.Heap.node 0 Batteries.PairingHeapImp.Heap.nil Batteries.PairingHeapImp.Heap.nil)) (Batteries.PairingHeapImp.Heap.nil)) (by
  decide +kernel)

-- List.beq_iff_exists_findIdxNth, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.beq_iff_exists_findIdxNth.h5 : ¬∀ {α : Type} {i : Nat} {x : α} [inst : BEq α] {xs : List α}, i < xs.length := fun hc_h => absurd (@hc_h (Nat) (0) (0) (instBEqOfDecidableEq) ([])) (by
  decide +kernel)

-- Batteries.PairingHeapImp.Heap.size_deleteMin_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.PairingHeapImp.Heap.size_deleteMin_lt.h5 : ¬∀ {α : Type} {le : α → α → Bool} {a : α} {s' s : Batteries.PairingHeapImp.Heap α}, s'.size < s.size := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Bool) (0) (Batteries.PairingHeapImp.Heap.nil) (Batteries.PairingHeapImp.Heap.nil)) (by
  decide +kernel)

-- Substring.Raw.ValidFor.take, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.ValidFor.take.h4 : ¬∀ {l m r : List Char} {s : Substring.Raw} (n : Nat),
        Substring.Raw.ValidFor l (List.take n m) (List.drop n m ++ r) (s.take n) := fun hc_h => absurd (@hc_h ([]) ([]) ([]) ({ str := "a", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw }) (0)) (by
  decide +kernel)

-- Substring.Raw.ValidFor.contains, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.ValidFor.contains.h5 : ¬∀ {l : List Char} {m : List Char} {r : List Char} (c : Char) {s : Substring.Raw},
        Substring.Raw.Legacy.contains s c = Bool.true ↔ c ∈ m := fun hc_h => absurd (@hc_h ([]) (['a']) ([]) ('a') ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw })) (by
  decide +kernel)

-- List.idxOf_add_mem_idxsOf, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOf_add_mem_idxsOf.h5 : ¬∀ {α : Type} {xs : List α} {x : α} [inst : BEq α] (s : Nat), List.idxOf x xs + s ∈ List.idxsOf x xs s := fun hc_h => absurd (@hc_h (Nat) ([]) (0) (instBEqOfDecidableEq) (0)) (by
  decide +kernel)

-- String.utf8SetAux_of_valid, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.utf8SetAux_of_valid.h5 : ¬∀ (c' : Char) (cs cs' : List Char) {i p : Nat},
        String.Pos.Raw.utf8SetAux c' (cs ++ cs') { byteIdx := i : String.Pos.Raw } { byteIdx := p : String.Pos.Raw } =
          cs ++ List.modifyHead (fun (x : Char) => c') cs' := fun hc_h => absurd (@hc_h ('a') (['0']) ([]) (0) (0)) (by
  decide +kernel)

-- Vector.isSome_finIdxOf?, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.isSome_finIdxOf?.h3 : ¬∀ {α : Type} {n : Nat} [inst : BEq α] {v : Vector α n} {a : α}, (v.finIdxOf? a).isSome = v.contains a := fun hc_h => absurd (@hc_h (Nat) (1) (⟨fun a b => a ≤ b⟩ : BEq Nat) (#v[0]) (1)) (by
  decide +kernel)

-- List.mem_union_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_union_iff.h2 : ¬∀ {α : Type} [inst : BEq α] {x : α} {l₁ l₂ : List α}, x ∈ l₁ ∪ l₂ ↔ x ∈ l₁ ∨ x ∈ l₂ := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (0) ([0]) ([1])) (by
  decide +kernel)

-- Substring.Raw.ValidFor.any, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.ValidFor.any.h5 : ¬∀ {l : List Char} {m : List Char} {r : List Char} (f : Char → Bool) {s : Substring.Raw},
        Substring.Raw.Legacy.any s f = m.any f := fun hc_h => absurd (@hc_h ([]) (['a']) ([]) (fun (a : Char) => Bool.true) ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw })) (by
  decide +kernel)

-- List.insertP_cons_pos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.insertP_cons_pos.h5 : ¬∀ {α : Type} (p : α → Bool) (a b : α) (l : List α), List.insertP p a (b :: l) = a :: b :: l := fun hc_h => absurd (@hc_h (Nat) (fun n => n % 2 == 0 : Nat → Bool) (0) (1) ([])) (by
  decide +kernel)

-- List.getElem_getElem_idxsOf, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_getElem_idxsOf.h5 : ¬∀ {α : Type} {i : Nat} {xs : List α} {x : α} [inst : BEq α], i < (List.idxsOf x xs).length := fun hc_h => absurd (@hc_h (Nat) (0) ([]) (0) (instBEqOfDecidableEq)) (by
  decide +kernel)

-- List.getElem?_set_of_lt', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem?_set_of_lt'.h5 : ¬∀ {α : Type} (a : α) {m n : Nat} (l : List α), (l.set m a)[n]? = if m = n then Option.some a else l[n]? := fun hc_h => absurd (@hc_h (Nat) (0) (0) (0) ([])) (by
  decide +kernel)

-- Substring.Raw.ValidFor.dropWhile, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.ValidFor.dropWhile.h5 : ¬∀ {l m r : List Char} (p : Char → Bool) {s : Substring.Raw},
        Substring.Raw.ValidFor (l ++ List.takeWhile p m) (List.dropWhile p m) r (s.dropWhile p) := fun hc_h => absurd (@hc_h ([]) ([]) ([]) (fun (a : Char) => Bool.false) ({ str := "a", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw })) (by
  decide +kernel)

-- Substring.Raw.ValidFor.atEnd, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.ValidFor.atEnd.h5 : ¬∀ {l : List Char} {m : List Char} {r : List Char} {p : Nat} {s : Substring.Raw},
        s.atEnd { byteIdx := p : String.Pos.Raw } = Bool.true ↔ p = String.utf8Len m := fun hc_h => absurd (@hc_h ([]) (['a']) ([]) (0) ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw })) (by
  decide +kernel)

-- List.interleave_append_append_of_length_eq_length, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.interleave_append_append_of_length_eq_length.h3 : ¬∀ {α : Type} {l₁ l₂ : List α} (l₃ l₄ : List α), (l₁ ++ l₃).interleave (l₂ ++ l₄) = l₁.interleave l₂ ++ l₃.interleave l₄ := fun hc_h => absurd (@hc_h (Nat) ([]) ([0]) ([1]) ([])) (by
  decide +kernel)

-- Substring.Raw.ValidFor.drop, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.ValidFor.drop.h4 : ¬∀ {l m r : List Char} {s : Substring.Raw} (n : Nat),
        Substring.Raw.ValidFor (l ++ List.take n m) (List.drop n m) r (s.drop n) := fun hc_h => absurd (@hc_h ([]) ([]) ([]) ({ str := "a", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw }) (0)) (by
  decide +kernel)

-- List.diff_cons, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.diff_cons.h2 : ¬∀ {α : Type} [inst : BEq α] (l₁ l₂ : List α) (a : α), l₁.diff (a :: l₂) = (l₁.erase a).diff l₂ := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : BEq Nat) ([0]) ([]) (1)) (by
  decide +kernel)

-- Substring.Raw.ValidFor.front, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.ValidFor.front.h5 : ¬∀ {l : List Char} {c : Char} {m r : List Char} {s : Substring.Raw}, s.front = c := fun hc_h => absurd (@hc_h ([]) ('a') ([]) ([]) ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw })) (by
  decide +kernel)

-- String.lt_antisymm, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.lt_antisymm.h2 : ¬∀ {s₁ s₂ : String}, ¬s₂ < s₁ → s₁ = s₂ := fun hc_h => absurd (@hc_h ("") ("a") (by
  decide)) (by
  decide +kernel)

-- String.lt_antisymm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.lt_antisymm.h3 : ¬∀ {s₁ s₂ : String}, ¬s₁ < s₂ → s₁ = s₂ := fun hc_h => absurd (@hc_h ("a") ("") (by
  decide)) (by
  decide +kernel)

-- Batteries.UnionFind.rank'_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.UnionFind.rank'_lt.h2 : ¬∀ (self : Batteries.UnionFind) (i : Nat), i < self.arr.size := fun hc_h => absurd (@hc_h (Batteries.UnionFind.empty : Batteries.UnionFind) (0)) (by
  decide +kernel)

-- Batteries.UnionFind.rank'_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.UnionFind.rank'_lt.h3 : ¬∀ (self : Batteries.UnionFind) (i : Nat) (h : i < self.arr.size), self.rank i < self.rank self.arr[i].parent := fun hc_h => absurd (fun hc_k0 => @hc_h (Batteries.UnionFind.empty.push : Batteries.UnionFind) (0) hc_k0) (by
  decide +kernel)

-- List.findIdxNth_eq_findIdxNth_iff_of_left_lt_countP, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.findIdxNth_eq_findIdxNth_iff_of_left_lt_countP.h5 : ¬∀ {α : Type} {n : Nat} {p : α → Bool} {m : Nat} {xs : List α}, List.findIdxNth p xs n = List.findIdxNth p xs m ↔ n = m := fun hc_h => absurd (@hc_h (Nat) (0) (fun n => n % 2 == 0 : Nat → Bool) (1) ([])) (by
  decide +kernel)

-- congr_arg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.congr_arg.h5 : ¬∀ {α β : Type} {a₁ a₂ : α} (f : α → β), f a₁ = f a₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (0) (1) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- List.pwFilter_cons_of_pos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.pwFilter_cons_of_pos.h5 : ¬∀ {α : Type} {R : α → α → Prop} [inst : DecidableRel R] {a : α} {l : List α},
        List.pwFilter R (a :: l) = a :: List.pwFilter R l := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (Nat.decLt) (0) ([0])) (by
  decide +kernel)

-- List.pwFilter_cons_of_neg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.pwFilter_cons_of_neg.h5 : ¬∀ {α : Type} {R : α → α → Prop} [inst : DecidableRel R] {a : α} {l : List α},
        List.pwFilter R (a :: l) = List.pwFilter R l := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (Nat.decLt) (0) ([])) (by
  decide +kernel)

-- List.insertP_cons_neg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.insertP_cons_neg.h5 : ¬∀ {α : Type} (p : α → Bool) (a b : α) (l : List α), List.insertP p a (b :: l) = b :: List.insertP p a l := fun hc_h => absurd (@hc_h (Nat) (fun n => n % 2 == 0 : Nat → Bool) (1) (0) ([])) (by
  decide +kernel)

-- Std.LawfulLECmp.ne_gt_iff_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.LawfulLECmp.ne_gt_iff_le.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {x y : α} [inst : LE α], cmp x y ≠ Ordering.gt ↔ x ≤ y := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare (a / 2) (b / 2) : Nat → Nat → Ordering) (1) (0) (instLENat)) (by
  decide +kernel)

-- List.getElem_findIdxs_eq_findIdxNth_add, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_findIdxs_eq_findIdxNth_add.h5 : ¬∀ {α : Type} {n : Nat} {p : α → Bool} {s : Nat} {xs : List α}, n < (List.findIdxs p xs s).length := fun hc_h => absurd (@hc_h (Nat) (0) (fun n => n % 2 == 0 : Nat → Bool) (0) ([])) (by
  decide +kernel)

-- List.forall_mem_pwFilter, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.forall_mem_pwFilter.h3 : ¬∀ {α : Type} {R : α → α → Prop} [inst : DecidableRel R] (a : α) (l : List α),
        (∀ (b : α), b ∈ List.pwFilter R l → R a b) ↔ ∀ (b : α), b ∈ l → R a b := fun hc_h => absurd (@hc_h (Nat) (fun a b => a = b : Nat → Nat → Prop) (instDecidableEqNat) (0) ([1, 0])) (by
  decide +kernel)

-- List.set_eq_take_cons_drop, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.set_eq_take_cons_drop.h4 : ¬∀ {α : Type} (a : α) {n : Nat} {l : List α}, l.set n a = List.take n l ++ a :: List.drop (n + 1) l := fun hc_h => absurd (@hc_h (Nat) (0) (0) ([])) (by
  decide +kernel)

-- List.disjoint_of_disjoint_append_right_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.disjoint_of_disjoint_append_right_left.h4 : ¬∀ {α : Type} {l l₁ : List α} {l₂ : List α}, l.Disjoint l₁ := fun hc_h => absurd (@hc_h (Nat) ([0]) ([0]) ([])) (by
  simp)

-- List.mem_findIdxs_iff_pos_getElem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_findIdxs_iff_pos_getElem.h4 : ¬∀ {i : Nat} {α : Type} {xs : List α} {p : α → Bool}, i < xs.length := fun hc_h => absurd (@hc_h (0) (Nat) ([]) (fun n => n % 2 == 0 : Nat → Bool)) (by
  decide +kernel)

-- List.Perm.subperm_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.subperm_right.h4 : ¬∀ {α : Type} {l₁ l₂ l : List α}, l₁.Subperm l ↔ l₂.Subperm l := fun hc_h => absurd (@hc_h (Nat) ([]) ([0]) ([])) (by
  decide +kernel)

-- Std.LawfulCmp.toLawfulLTCmp, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.LawfulCmp.toLawfulLTCmp.h4 : ¬∀ {α : Type} [inst : LE α] [inst : LT α] {cmp : α → α → Ordering}, Std.LawfulLTCmp cmp := fun hc_h => absurd (@hc_h (Nat) (instLENat) (instLTNat) (fun a b => compare (a / 2) (b / 2) : Nat → Nat → Ordering)) (by
  exact fun hc_c =>
    absurd (hc_c.eq_lt_iff_lt (x := (0 : Nat)) (y := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.isSubperm_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.isSubperm_iff.h2 : ¬∀ {α : Type} [inst : BEq α] {l₁ l₂ : List α}, l₁.isSubperm l₂ = Bool.true ↔ l₁.Subperm l₂ := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([0]) ([1])) (by
  decide +kernel)

-- List.getElem_zero_idxsOf_eq_idxOf, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_zero_idxsOf_eq_idxOf.h4 : ¬∀ {α : Type} {xs : List α} {x : α} [inst : BEq α], 0 < (List.idxsOf x xs).length := fun hc_h => absurd (@hc_h (Nat) ([]) (0) (instBEqOfDecidableEq)) (by
  decide +kernel)

-- List.subperm_cons_erase, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.subperm_cons_erase.h2 : ¬∀ {α : Type} [inst : BEq α] (a : α) (l : List α), l.Subperm (a :: l.erase a) := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (0) ([1])) (by
  decide +kernel)

-- List.countPBefore_of_ge_length, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.countPBefore_of_ge_length.h4 : ¬∀ {α : Type} {i : Nat} {p : α → Bool} {xs : List α}, List.countPBefore p xs i = List.countP p xs := fun hc_h => absurd (@hc_h (Nat) (0) (fun n => n % 2 == 0 : Nat → Bool) ([0])) (by
  decide +kernel)

-- List.swap_eq_of_ge_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.swap_eq_of_ge_right.h4 : ¬∀ {α : Type} {j i : Nat} {xs : List α}, xs.swap i j = xs := fun hc_h => absurd (@hc_h (Nat) (0) (1) ([0, 1])) (by
  decide +kernel)

-- Std.LawfulCmp.toTransCmp, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.LawfulCmp.toTransCmp.h4 : ¬∀ {α : Type} {inst : LE α} {inst : LT α} {cmp : α → α → Ordering}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (instLENat) (instLTNat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.sum_zero_cons, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.sum_zero_cons.h3 : ¬∀ {α : Type} [inst : Add α] [inst_1 : Zero α] {l : List α}, (0 :: l).sum = l.sum := fun hc_h => absurd (@hc_h (Nat) (instAddNat) (⟨1⟩ : Zero Nat) ([])) (by
  decide +kernel)

-- List.getElem_swap_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_swap_left.h4 : ¬∀ {α : Type} {xs : List α} {i j : Nat}, i < (xs.swap i j).length := fun hc_h => absurd (@hc_h (Nat) ([]) (0) (0)) (by
  decide +kernel)

-- Std.instTransCmpByKey, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.instTransCmpByKey.h4 : ¬∀ {α β : Type} (f : α → β) (cmp : β → β → Ordering), Std.TransCmp (Ordering.byKey f cmp) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun n => n + 1 : Nat → Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.diff_eq_foldl, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.diff_eq_foldl.h2 : ¬∀ {α : Type} [inst : BEq α] (l₁ l₂ : List α), l₁.diff l₂ = List.foldl List.erase l₁ l₂ := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : BEq Nat) ([0]) ([1])) (by
  decide +kernel)

-- List.Pairwise.isChain, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.isChain.h3 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α}, List.IsChain R l := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) ([1, 0])) (by
  decide +kernel)

-- BitVec.getElem_ofFnLE, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.BitVec.getElem_ofFnLE.h3 : ¬∀ {n : Nat} (f : Fin n → Bool) (i : Nat), i < n := fun hc_h => absurd (@hc_h (0) (fun (a : Fin 0) => Bool.false) (0)) (by
  decide +kernel)

-- String.Legacy.Iterator.ValidFor.remainingToString, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Legacy.Iterator.ValidFor.remainingToString.h3 : ¬∀ {l : List Char} {r : List Char} {it : String.Legacy.Iterator}, it.remainingToString = String.ofList r := fun hc_h => absurd (@hc_h ([]) (['a']) ({ s := "", i := { : String.Pos.Raw } : String.Legacy.Iterator })) (by
  decide +kernel)

-- Std.LawfulLTCmp.toOrientedCmp, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.LawfulLTCmp.toOrientedCmp.h3 : ¬∀ {α : Type} {inst : LT α} {cmp : α → α → Ordering}, Std.OrientedCmp cmp := fun hc_h => absurd (@hc_h (Nat) (instLTNat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering)) (by
  exact fun hc_c =>
    absurd (hc_c.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- String.Legacy.Iterator.ValidFor.hasNext, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Legacy.Iterator.ValidFor.hasNext.h3 : ¬∀ {l : List Char} {r : List Char} {it : String.Legacy.Iterator}, it.hasNext = Bool.true ↔ r ≠ [] := fun hc_h => absurd (@hc_h ([]) (['a']) ({ s := "", i := { : String.Pos.Raw } : String.Legacy.Iterator })) (by
  decide +kernel)

-- String.Legacy.Iterator.ValidFor.toEnd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Legacy.Iterator.ValidFor.toEnd.h3 : ¬∀ {l r : List Char} {it : String.Legacy.Iterator}, String.Legacy.Iterator.ValidFor (r.reverse ++ l) [] it.toEnd := fun hc_h => absurd (@hc_h ([]) (['a']) ({ s := "", i := { : String.Pos.Raw } : String.Legacy.Iterator })) (by
  decide +kernel)

-- List.rightInverse_sigmaCountToIdx_idxToSigmaCount, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.rightInverse_sigmaCountToIdx_idxToSigmaCount.h2 : ¬∀ {α : Type} [inst : BEq α] {xs : List α}, LawfulBEq α := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([])) (by
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

-- Batteries.UnionFind.rootD_ext, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.UnionFind.rootD_ext.h2 : ¬∀ {m1 m2 : Batteries.UnionFind} {x : Nat}, m1.rootD x = m2.rootD x := fun hc_h => absurd (@hc_h (Batteries.UnionFind.empty : Batteries.UnionFind) (Batteries.UnionFind.empty.push.push.union! 0 1 : Batteries.UnionFind) (0)) (by
  decide +kernel)

-- Batteries.UnionFind.parentD_findAux_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.UnionFind.parentD_findAux_lt.h3 : ¬∀ {i : Nat} {self : Batteries.UnionFind} {x : Fin self.size},
        Batteries.UnionFind.parentD (self.findAux x).s i < self.size := fun hc_h => absurd (@hc_h (1) (Batteries.UnionFind.empty.push : Batteries.UnionFind) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Batteries.UnionFind.Equiv.symm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.UnionFind.Equiv.symm.h3 : ¬∀ {self : Batteries.UnionFind} {a b : Nat}, self.Equiv b a := fun hc_h => absurd (@hc_h (Batteries.UnionFind.empty : Batteries.UnionFind) (0) (1)) (by
  simp)

-- List.dropLast_eq_eraseIdx, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.dropLast_eq_eraseIdx.h3 : ¬∀ {α : Type} {xs : List α} {i : Nat}, xs.dropLast = xs.eraseIdx i := fun hc_h => absurd (@hc_h (Nat) ([0]) (1)) (by
  decide +kernel)

-- Nat.testBit_ofBits_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.testBit_ofBits_lt.h3 : ¬∀ {n : Nat} (f : Fin n → Bool) (i : Nat), i < n := fun hc_h => absurd (@hc_h (0) (fun (a : Fin 0) => Bool.false) (0)) (by
  decide +kernel)

-- List.Sublist.subperm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Sublist.subperm.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁.Subperm l₂ := fun hc_h => absurd (@hc_h (Nat) ([0]) ([])) (by
  decide +kernel)

-- List.rightInverse_idxToSigmaCount_sigmaCountToIdx, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.rightInverse_idxToSigmaCount_sigmaCountToIdx.h2 : ¬∀ {α : Type} [inst : BEq α] {xs : List α}, ReflBEq α := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a != b⟩ : BEq Nat) ([])) (by
  exact fun hc_c =>
    absurd (hc_c.rfl (a := (0 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.Perm.subperm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.subperm.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁.Subperm l₂ := fun hc_h => absurd (@hc_h (Nat) ([0]) ([])) (by
  decide +kernel)

-- Nat.testBit_ofBits_ge, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.testBit_ofBits_ge.h3 : ¬∀ {n : Nat} (f : Fin n → Bool) (i : Nat), (Nat.ofBits f).testBit i = Bool.false := fun hc_h => absurd (@hc_h (1) (fun (a : Fin 1) => Bool.true) (0)) (by
  decide +kernel)

-- List.leftInverse_idxToSigmaCount_sigmaCountToIdx, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.leftInverse_idxToSigmaCount_sigmaCountToIdx.h2 : ¬∀ {α : Type} [inst : BEq α] {xs : List α}, LawfulBEq α := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([])) (by
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

-- List.findIdx_mem_findIdxs, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.findIdx_mem_findIdxs.h3 : ¬∀ {α : Type} {xs : List α} {p : α → Bool}, List.findIdx p xs ∈ List.findIdxs p xs := fun hc_h => absurd (@hc_h (Nat) ([]) (fun n => n % 2 == 0 : Nat → Bool)) (by
  decide +kernel)

-- Array.heapSort_sorted, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.heapSort_sorted.h2 : ¬∀ {α : Type} [instOrd : Ord α] {a : Array α},
        List.Pairwise (fun (x1 x2 : α) => (Ord.compare x1 x2).isLE = Bool.true) a.heapSort.toList := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => if a % 3 = b % 3 then .eq else if (a + 1) % 3 = b % 3 then .lt else .gt⟩ : Ord Nat) (#[0, 1, 2])) (by
  decide +kernel)

-- String.utf8Len_le_of_prefix, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.utf8Len_le_of_prefix.h2 : ¬∀ {cs₁ cs₂ : List Char}, String.utf8Len cs₁ ≤ String.utf8Len cs₂ := fun hc_h => absurd (@hc_h (['a']) ([])) (by
  decide +kernel)

-- List.length_tail_add_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.length_tail_add_one.h2 : ¬∀ {α : Type} (l : List α), l.tail.length + 1 = l.length := fun hc_h => absurd (@hc_h (Nat) ([])) (by
  decide +kernel)

-- UInt8.ext, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.UInt8.ext.h2 : ¬∀ {x y : UInt8}, x = y := fun hc_h => absurd (@hc_h (UInt8.ofNat 0) (UInt8.ofNat 1)) (by
  decide +kernel)

-- Fin.exists_eq_true_of_isSome_find?, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.exists_eq_true_of_isSome_find?.h2 : ¬∀ {n : Nat} {p : Fin n → Bool}, ∃ (i : Fin n), p i = Bool.true := fun hc_h => absurd (@hc_h (0) (fun (a : Fin 0) => Bool.false)) (by
  decide +kernel)

-- ByteArray.getElem_eq_data_getElem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ByteArray.getElem_eq_data_getElem.h2 : ¬∀ {i : Nat} (a : ByteArray), i < a.size := fun hc_h => absurd (@hc_h (0) ({ data := #[] : ByteArray })) (by
  decide +kernel)

-- String.utf8Len_le_of_suffix, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.utf8Len_le_of_suffix.h2 : ¬∀ {cs₁ cs₂ : List Char}, String.utf8Len cs₁ ≤ String.utf8Len cs₂ := fun hc_h => absurd (@hc_h (['a']) ([])) (by
  decide +kernel)

-- Batteries.UnionFind.parent'_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.UnionFind.parent'_lt.h2 : ¬∀ (self : Batteries.UnionFind) (i : Nat), i < self.arr.size := fun hc_h => absurd (@hc_h (Batteries.UnionFind.empty : Batteries.UnionFind) (0)) (by
  decide +kernel)

-- Batteries.UnionFind.rank'_lt_rankMax, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.UnionFind.rank'_lt_rankMax.h2 : ¬∀ (self : Batteries.UnionFind) (i : Nat), i < self.arr.size := fun hc_h => absurd (@hc_h (Batteries.UnionFind.empty : Batteries.UnionFind) (0)) (by
  decide +kernel)

-- Batteries.UnionFind.rankD_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.UnionFind.rankD_eq.h2 : ¬∀ {arr : Array Batteries.UFNode} {i : Nat}, i < arr.size := fun hc_h => absurd (@hc_h (#[]) (0)) (by
  decide +kernel)

-- Char.toUpper_eq_of_isLower, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Char.toUpper_eq_of_isLower.h1 : ¬∀ {c : Char}, c.toUpper = Char.ofNat (c.toNat - 32) := fun hc_h => absurd (@hc_h ('0')) (by
  decide +kernel)

